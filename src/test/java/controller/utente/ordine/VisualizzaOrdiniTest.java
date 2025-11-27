package controller.utente.ordine;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.util.List;

import static org.mockito.Mockito.*;

class VisualizzaOrdiniTest {
    private VisualizzaOrdini servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private Utente utente;
    private OrdineDAO ordineDAO;

    @BeforeEach
    void setUp() {
        servletUnderTest = new VisualizzaOrdini();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        utente = mock(Utente.class);
        ordineDAO = mock(OrdineDAO.class);
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utente);
        when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
            // Imposto valore di default per getTipo per evitare NPE
            when(utente.getTipo()).thenReturn("");
    }

    @Test
    void testDoGet_UserIsAdmin() throws ServletException, IOException {
    // Simulo utente admin (Validator si aspetta un tipo che inizi con "Gestore")
    when(utente.getTipo()).thenReturn("Gestore");
        servletUnderTest.doGet(request, response);
        verify(request).getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_UserIsNotAdmin() throws ServletException, IOException {
           // Simulo utente non admin
           when(utente.getTipo()).thenReturn("user");
           when(utente.getEmail()).thenReturn("test@email.com");
        // Mock OrdineDAO e risultato - lo iniettiamo nella servlet
        OrdineDAO ordineDAOMock = mock(OrdineDAO.class);
        List<Ordine> ordini = List.of(mock(Ordine.class));
        when(ordineDAOMock.doRetrieveByUtente("test@email.com")).thenReturn(ordini);
        servletUnderTest.setOrdineDAO(ordineDAOMock);
           servletUnderTest.doGet(request, response);
           verify(session).setAttribute(eq("ordini"), eq(ordini));
           verify(request).getRequestDispatcher("/WEB-INF/results/areaPservices/visualizzaOrdini.jsp");
           verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_UserIsNotAdmin_WithNullDAO() throws ServletException, IOException {
        // Test the case where ordineDAO is NOT injected (null)
        // This forces the servlet to use: new OrdineDAO()
        when(utente.getTipo()).thenReturn("user");
        when(utente.getEmail()).thenReturn("test@email.com");
        
        // DO NOT inject OrdineDAO - leave it null
        // Mock the construction of OrdineDAO to prevent real database connection
        try (MockedConstruction<OrdineDAO> mocked = mockConstruction(OrdineDAO.class,
                (mock, context) -> {
                    List<Ordine> ordini = List.of(mock(Ordine.class));
                    when(mock.doRetrieveByUtente("test@email.com")).thenReturn(ordini);
                })) {
            
            servletUnderTest.doGet(request, response);
            
            // Verify that setAttribute was called with "ordini" key
            verify(session).setAttribute(eq("ordini"), any(List.class));
            verify(request).getRequestDispatcher("/WEB-INF/results/areaPservices/visualizzaOrdini.jsp");
            verify(dispatcher).forward(request, response);
        }
    }
}
