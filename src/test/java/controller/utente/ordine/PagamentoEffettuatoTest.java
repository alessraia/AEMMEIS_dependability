package controller.utente.ordine;

import controller.utente.ordine.PagamentoEffettuato;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.*;
import model.tesseraService.Tessera;
import model.tesseraService.TesseraDAO;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.io.IOException;

import static org.mockito.Mockito.*;

class PagamentoEffettuatoTest {

    private PagamentoEffettuato servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private TesseraDAO tesseraDAO;

    @BeforeEach
    void setUp() {
        servletUnderTest = new PagamentoEffettuato();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        tesseraDAO = mock(TesseraDAO.class);
        
        servletUnderTest.setTesseraDAO(tesseraDAO);
        when(request.getSession()).thenReturn(session);
    }

    /**
     * Flusso alternativo: campi carta errati
     * UC_GO_4.2 scenario 3.a
     */
    @Test
    void testDoGet_InvalidCardData() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("Standard");
        when(session.getAttribute("utente")).thenReturn(user);
        // Parametri carta
        when(request.getParameter("cardName")).thenReturn("");
        when(request.getParameter("cardNumber")).thenReturn("abc123");
        when(request.getParameter("expiryDate")).thenReturn(null);
        when(request.getParameter("cvv")).thenReturn("xyz");
        when(request.getParameter("costo")).thenReturn("1.0");

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    /**
     * Flusso alternativo: premium con punti > disponibili (UC_GO_4.4 scenario 4.a1)
     */
    @Test
    void testDoGet_InvalidPoints() throws ServletException, IOException {
        Utente premiumUser = new Utente();
        premiumUser.setTipo("Premium");
        premiumUser.setEmail("alice@gmail.com");
        when(session.getAttribute("utente")).thenReturn(premiumUser);
        Tessera tessera = new Tessera();
        tessera.setPunti(900);
        when(tesseraDAO.doRetrieveByEmail("alice@gmail.com")).thenReturn(tessera);

        // Simuliamo che l'utente inserisce 999 punti, ma in DB ne ha meno
        when(request.getParameter("punti")).thenReturn("999");
        // Campi carta validi
        when(request.getParameter("cardName")).thenReturn("Mario Rossi");
        when(request.getParameter("cardNumber")).thenReturn("1234567890123456");
        when(request.getParameter("expiryDate")).thenReturn("2025-12-31");
        when(request.getParameter("cvv")).thenReturn("123");
        when(request.getParameter("costo")).thenReturn("1.0");

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    /**
     * Flusso principale: utente standard con campi validi -> ordineEffettuato.jsp
     */
    @Test
    void testDoGet_SuccessStandard() throws ServletException, IOException {
        Utente standardUser = new Utente();
        standardUser.setTipo("standard");
        standardUser.setEmail("mario@example.com");
        when(session.getAttribute("utente")).thenReturn(standardUser);

        when(request.getParameter("cardName")).thenReturn("Mario Rossi");
        when(request.getParameter("cardNumber")).thenReturn("1234567890123456");
        when(request.getParameter("expiryDate")).thenReturn("2025-12-31");
        when(request.getParameter("cvv")).thenReturn("123");

        // Indirizzo e costo
        when(request.getParameter("indirizzo")).thenReturn("Via Prova 1");
        when(request.getParameter("citta")).thenReturn("Roma");
        when(request.getParameter("costo")).thenReturn("39.90");

        when(request.getRequestDispatcher("/WEB-INF/results/ordineEffettuato.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }
}
