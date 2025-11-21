package controller.utente.ordine;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.ordineService.Ordine;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.mockito.Mockito.*;

class PuntiServletTest {
    private PuntiServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private Utente utente;

    @BeforeEach
    void setUp() {
        servletUnderTest = new PuntiServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        utente = mock(Utente.class);
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utente);
        // Imposto valore di default per getTipo per evitare NPE nei test
        when(utente.getTipo()).thenReturn("");
        when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
    }

    @Test
    void testDoGet_UserIsAdmin() throws ServletException, IOException {
        // Simulo utente admin (Validator controlla che getTipo() inizi con "Gestore")
        when(utente.getTipo()).thenReturn("Gestore");
        servletUnderTest.doGet(request, response);
        verify(request).getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_UserIsNotAdmin() throws ServletException, IOException {
        when(utente.getTipo()).thenReturn("user");
        when(request.getParameter("citta")).thenReturn("Roma");
        when(request.getParameter("indirizzo")).thenReturn("Via Test");
        when(request.getParameter("punti")).thenReturn("10");
        when(request.getParameter("costo")).thenReturn("100.0");
        servletUnderTest.doGet(request, response);
        verify(request).getRequestDispatcher("/WEB-INF/results/pagamentoOrdine.jsp");
        verify(dispatcher).forward(request, response);
        verify(request).setAttribute(eq("ordine"), any(Ordine.class));
        verify(request).setAttribute(eq("costo"), any());
    }
}
