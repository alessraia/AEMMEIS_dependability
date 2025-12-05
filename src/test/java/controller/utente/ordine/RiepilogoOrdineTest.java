package controller.utente.ordine;

import controller.utente.ordine.RiepilogoOrdinePackage.RiepilogoOrdine;
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

import java.io.IOException;

import static org.mockito.Mockito.*;

class RiepilogoOrdineTest {
    private RiepilogoOrdine servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private Utente utente;

    @BeforeEach
    void setUp() {
        servletUnderTest = new RiepilogoOrdine();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        utente = mock(Utente.class);
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utente);
        // default getTipo to avoid NPE
        when(utente.getTipo()).thenReturn("");
        when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
    }

    @Test
    void testDoGet_UserIsAdmin() throws ServletException, IOException {
        when(utente.getTipo()).thenReturn("Gestore");
        servletUnderTest.doGet(request, response);
        verify(request).getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_UserIsNotAdmin() throws ServletException, IOException {
        when(utente.getTipo()).thenReturn("user");
        when(request.getParameter("idOrdine")).thenReturn("123");
        OrdineDAO ordineDAOMock = mock(OrdineDAO.class);
        Ordine ordine = mock(Ordine.class);
        when(ordineDAOMock.doRetrieveById("123")).thenReturn(ordine);
        servletUnderTest.setOrdineDAO(ordineDAOMock);

        servletUnderTest.doGet(request, response);

        verify(session).setAttribute(eq("ordine"), any(Ordine.class));
        verify(request).getRequestDispatcher("/WEB-INF/results/areaPservices/riepilogoOrdine.jsp");
        verify(dispatcher).forward(request, response);
    }
}
